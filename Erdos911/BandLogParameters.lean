import Erdos911.BandDegreeParameters

namespace Erdos911

theorem band_low_degree_bound (q : ℕ) (hq : 131072 ≤ q)
    (hd : 131072 ≤ bandDegree q) (hlog : 1 ≤ Real.log (bandDegree q)) :
    bandLeftThreshold q + 2 * q ≤
      524288 * bandDegree q * (Real.log (bandDegree q)) ^ nearRegularDegreePower := by
  have hqd := (bandDegree_bounds q hq).2.2.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdpos : (0 : ℝ) < bandDegree q := by exact_mod_cast (show 0 < bandDegree q by omega)
  have hqR : (q : ℝ) ≤ 131072 * bandDegree q := by exact_mod_cast hqd
  have hdR : (131072 : ℝ) ≤ bandDegree q := by exact_mod_cast hd
  have hsquare : (q : ℝ) ≤ (bandDegree q : ℝ) ^ 2 := by nlinarith only [hqR, hdR]
  have hlogs : Real.log q ≤ 2 * Real.log (bandDegree q) := by
    have h := Real.log_le_log hqpos hsquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hκ : 0 ≤ nearRegularDegreePower := by norm_num [nearRegularDegreePower]
  have hκ1 : nearRegularDegreePower ≤ 1 := by norm_num [nearRegularDegreePower]
  have htwo : (2 : ℝ) ^ nearRegularDegreePower ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hκ1
  have hpow : (Real.log q) ^ nearRegularDegreePower ≤
      2 * (Real.log (bandDegree q)) ^ nearRegularDegreePower := by
    calc
      _ ≤ (2 * Real.log (bandDegree q)) ^ nearRegularDegreePower := Real.rpow_le_rpow hlogq hlogs hκ
      _ = (2 : ℝ) ^ nearRegularDegreePower * (Real.log (bandDegree q)) ^ nearRegularDegreePower :=
        Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by linarith) _)
  have hpow1 : 1 ≤ (Real.log (bandDegree q)) ^ nearRegularDegreePower := Real.one_le_rpow hlog hκ
  have hT := mul_le_mul_of_nonneg_left hpow hqpos.le
  have hQ := mul_le_mul_of_nonneg_right hqR
    (Real.rpow_nonneg (by linarith : 0 ≤ Real.log (bandDegree q)) nearRegularDegreePower)
  have hunit := mul_le_mul_of_nonneg_left hpow1 hqpos.le
  unfold bandLeftThreshold
  nlinarith only [hT, hQ, hunit]

theorem band_high_degree_bound (q : ℕ) (hq : 131072 ≤ q)
    (hlog : 1 ≤ Real.log q)
    (hlarge : 64 ≤ (Real.log q) ^ (nearRegularDegreePower / 2)) :
    (bandDegree q : ℝ) * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
      (bandDegree q : ℝ) / (2 * q) * bandLeftFloor q / 2 := by
  have hd := (bandDegree_bounds q hq).1
  have hdq := (bandDegree_bounds q hq).2.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdpos : (0 : ℝ) < bandDegree q := by exact_mod_cast (show 0 < bandDegree q by omega)
  have hlogpos : 0 < Real.log q := by linarith
  have hlogd : 0 ≤ Real.log (bandDegree q) := Real.log_nonneg (by exact_mod_cast hd)
  have hlogle : Real.log (bandDegree q) ≤ Real.log q :=
    Real.log_le_log hdpos (by exact_mod_cast hdq)
  have hhalf : (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
      (Real.log q) ^ (nearRegularDegreePower / 2) :=
    Real.rpow_le_rpow hlogd hlogle (by norm_num [nearRegularDegreePower])
  have hsquare : (Real.log q) ^ (nearRegularDegreePower / 2) *
      (Real.log q) ^ (nearRegularDegreePower / 2) = (Real.log q) ^ nearRegularDegreePower := by
    rw [← Real.rpow_add hlogpos]
    congr 1
    ring
  have hgap : 64 * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
      (Real.log q) ^ nearRegularDegreePower := by
    have h₁ := mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 64 by norm_num)
    have h₂ := mul_le_mul_of_nonneg_right hlarge
      (Real.rpow_nonneg hlogpos.le (nearRegularDegreePower / 2))
    rw [hsquare] at h₂
    exact h₁.trans h₂
  have hfloor := bandLeftFloor_lower q (by omega) hlog
  have hmean : (bandDegree q : ℝ) * (Real.log q) ^ nearRegularDegreePower / 64 ≤
      (bandDegree q : ℝ) / (2 * q) * bandLeftFloor q / 2 := by
    calc
      _ = (bandDegree q : ℝ) / (2 * q) * (bandLeftThreshold q / 16) / 2 := by
        unfold bandLeftThreshold
        field_simp
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfloor (by positivity)) (by norm_num)
  apply le_trans ?_ hmean
  have h := mul_le_mul_of_nonneg_left hgap hdpos.le
  nlinarith only [h]

end Erdos911
