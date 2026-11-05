import Erdos911.HeavyIncidenceExtraction

namespace Erdos911

/-- The polynomial dictionary gain, if established, absorbs every
edge lost in the heavy-block extraction, uniformly in the left scale. -/
theorem heavy_extraction_gain (d : ℕ) (M : ℝ) (hd : 2 ^ 32 ≤ d)
    (hM : M ≤ (d : ℝ)) :
    (M * d) * (128 * (d : ℝ) ^ 34) ≤ (7 / 16 : ℝ) * (heavyRowDegree d : ℝ) ^ 49 := by
  obtain ⟨_, hdq, _, _, _⟩ := heavy_packing_parameters d hd
  have hdqR : (d : ℝ) ≤ 8 * heavyRowDegree d := by exact_mod_cast hdq
  have hq : (2 ^ 29 : ℝ) ≤ heavyRowDegree d := by
    have hn : 2 ^ 29 ≤ heavyRowDegree d := by unfold heavyRowDegree; norm_num at hd ⊢; omega
    exact_mod_cast hn
  have hq13 : 128 * (8 : ℝ) ^ 36 ≤ (7 / 16 : ℝ) * (heavyRowDegree d : ℝ) ^ 13 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 ^ 29) hq 13
    norm_num at hh ⊢
    linarith only [hh]
  calc
    (M * d) * (128 * (d : ℝ) ^ 34) ≤ ((d : ℝ) * d) * (128 * (d : ℝ) ^ 34) := by gcongr
    _ = 128 * (d : ℝ) ^ 36 := by ring
    _ ≤ 128 * (8 * (heavyRowDegree d : ℝ)) ^ 36 := by gcongr
    _ = (128 * (8 : ℝ) ^ 36) * (heavyRowDegree d : ℝ) ^ 36 := by ring
    _ ≤ ((7 / 16 : ℝ) * (heavyRowDegree d : ℝ) ^ 13) * (heavyRowDegree d : ℝ) ^ 36 := by
      exact mul_le_mul_of_nonneg_right hq13 (by positivity)
    _ = (7 / 16 : ℝ) * (heavyRowDegree d : ℝ) ^ 49 := by ring

end Erdos911
