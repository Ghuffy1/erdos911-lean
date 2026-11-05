import Erdos911.RedPaletteCapacity

namespace Erdos911

/-- Sufficient pair-pattern density makes the total local-lemma weight
through a fixed host pair at most d^(-13). -/
theorem pair_pattern_weight_bound (D k d f : ℕ) (ρ : ℝ)
    (hD : 2 ≤ D) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hdense : 32 * (k : ℝ) * Real.log D ≤ ρ * f) :
    (k * D ^ (2 * (k - 1)) : ℕ) * Real.exp (-ρ * f / 2) ≤ 1 / (d : ℝ) ^ 13 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hkD : k ≤ D ^ k := (Nat.le_of_lt k.lt_two_pow_self).trans (Nat.pow_le_pow_left hD k)
  have hcount : k * D ^ (2 * (k - 1)) ≤ D ^ (3 * k) := by
    calc
      _ ≤ D ^ k * D ^ (2 * k) := Nat.mul_le_mul hkD (Nat.pow_le_pow_right (by omega) (by omega))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hcountExp : ((k * D ^ (2 * (k - 1)) : ℕ) : ℝ) ≤ Real.exp ((3 * (k : ℝ)) * Real.log D) := by
    have heq : Real.exp ((3 * (k : ℝ)) * Real.log D) = (D : ℝ) ^ (3 * k) := by
      rw [show 3 * (k : ℝ) = ((3 * k : ℕ) : ℝ) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log hDp]
    rw [heq]
    exact_mod_cast hcount
  have hproduct : (k * D ^ (2 * (k - 1)) : ℕ) * Real.exp (-ρ * f / 2) ≤
      Real.exp (-13 * (k : ℝ) * Real.log D) := by
    calc
      _ ≤ Real.exp (3 * (k : ℝ) * Real.log D) * Real.exp (-16 * (k : ℝ) * Real.log D) := by
        apply mul_le_mul hcountExp (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.exp_pos _).le
        linarith only [hdense]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpower : (d : ℝ) ≤ (D : ℝ) ^ k := by exact_mod_cast hdk.trans hkD
  have hdenom : (d : ℝ) ^ 13 ≤ ((D : ℝ) ^ k) ^ 13 := pow_le_pow_left₀ hdp.le hpower 13
  have hexp : Real.exp (-13 * (k : ℝ) * Real.log D) = 1 / ((D : ℝ) ^ k) ^ 13 := by
    rw [show -13 * (k : ℝ) * Real.log D = -((13 * k : ℕ) * Real.log D) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hDp, one_div]
    simp only [← pow_mul, Nat.mul_comm]
  rw [hexp] at hproduct
  exact hproduct.trans (one_div_le_one_div_of_le (pow_pos hdp 13) hdenom)

theorem pair_pattern_single_weight_bound (D k d f : ℕ) (ρ : ℝ)
    (hD : 2 ≤ D) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hdense : 32 * (k : ℝ) * Real.log D ≤ ρ * f) :
    Real.exp (-ρ * f / 2) ≤ 1 / (d : ℝ) ^ 13 := by
  have hk : 1 ≤ k := hd.trans hdk
  have hpower : 1 ≤ D ^ (2 * (k - 1)) := Nat.one_le_pow _ _ (by omega)
  have hc : (1 : ℝ) ≤ (k * D ^ (2 * (k - 1)) : ℕ) := by
    exact_mod_cast one_le_mul_of_one_le_of_one_le hk hpower
  have hm := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-ρ * f / 2)).le
  have hx : Real.exp (-ρ * f / 2) ≤
      (k * D ^ (2 * (k - 1)) : ℕ) * Real.exp (-ρ * f / 2) := by simpa only [one_mul] using hm
  exact hx.trans (pair_pattern_weight_bound D k d f ρ hD hd hdk hdense)

end Erdos911
