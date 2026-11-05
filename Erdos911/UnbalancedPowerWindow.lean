import Erdos911.UnbalancedNormalizationParameters

namespace Erdos911

/-- At the high-degree threshold used in the unrestricted reduction,
normalization lands in one fixed strongly unbalanced class. -/
theorem unbalanced_power_window (q p : ℕ) (Λ : ℝ)
    (hq : 2 ^ 64 ≤ q) (hp : q ^ 209 ≤ p) (_hΛ : 0 ≤ Λ) (hΛq : Λ ≤ (q : ℝ) ^ 2) :
    1 ≤ unbalancedRightDegree q ∧
      (unbalancedRightDegree q : ℝ) ^ 200 ≤ (p : ℝ) / 134217728 ∧
      5 * Λ * p ≤ (unbalancedRightDegree q : ℝ) ^ 4 * ((p : ℝ) / 134217728) := by
  have hqbase : 2097152 ≤ q := by norm_num at hq ⊢; omega
  have hqt : q ≤ 2097152 * unbalancedRightDegree q := by unfold unbalancedRightDegree; omega
  have ht : 2 ^ 43 ≤ unbalancedRightDegree q := by norm_num at hq ⊢; omega
  have htR : (8796093022208 : ℝ) ≤ unbalancedRightDegree q := by exact_mod_cast ht
  have hqtR : (q : ℝ) ≤ 2097152 * unbalancedRightDegree q := by exact_mod_cast hqt
  have htp : (0 : ℝ) < unbalancedRightDegree q := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpR : (q : ℝ) ^ 209 ≤ p := by exact_mod_cast hp
  have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast (show 8 ≤ q by norm_num at hq; omega)
  have hq9 : (134217728 : ℝ) ≤ (q : ℝ) ^ 9 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hq8 9
    norm_num only [show (8 : ℝ) ^ 9 = 134217728 by norm_num] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_left hq9 (pow_nonneg hqp.le 200)
  have hq209 : (q : ℝ) ^ 209 = (q : ℝ) ^ 200 * (q : ℝ) ^ 9 := by rw [← pow_add]
  have htq : (unbalancedRightDegree q : ℝ) ^ 200 ≤ (q : ℝ) ^ 200 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self q 1048576) 200
  have hP : (unbalancedRightDegree q : ℝ) ^ 200 ≤ (p : ℝ) / 134217728 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 134217728)]
    rw [hq209] at hpR
    nlinarith only [hmul, htq, hpR]
  have hq2 : (q : ℝ) ^ 2 ≤ 4398046511104 * (unbalancedRightDegree q : ℝ) ^ 2 := by
    nlinarith only [hqtR, htp, hqp]
  have ht2 : (2951479051793528258560 : ℝ) ≤ (unbalancedRightDegree q : ℝ) ^ 2 := by
    nlinarith only [htR]
  have hfour : 5 * 134217728 * Λ ≤ (unbalancedRightDegree q : ℝ) ^ 4 := by
    have hmul' := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (unbalancedRightDegree q : ℝ))
    nlinarith only [hmul', hq2, hΛq]
  have hpf : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
  have hmul' := mul_le_mul_of_nonneg_right hfour hpf
  exact ⟨by omega, hP, by nlinarith only [hmul']⟩

end Erdos911
