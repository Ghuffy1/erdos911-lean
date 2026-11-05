import Erdos911.PairPatternWeights
import Erdos911.PairMarkedRows

namespace Erdos911

noncomputable def lightPairProbability (d : ℕ) : ℝ := 1 / (d : ℝ) ^ 6
noncomputable def lightPairWeightBudget (d : ℕ) : ℝ := 1 / (d : ℝ) ^ 13
def lightPairTailFactor (d : ℕ) : ℕ := 16384 * d ^ 4

theorem light_pair_basic_parameters (d : ℕ) (hd : 65536 ≤ d) :
    0 ≤ lightPairProbability d ∧ lightPairProbability d ≤ 1 ∧
      0 ≤ lightPairWeightBudget d ∧ 4 * lightPairWeightBudget d ≤ lightPairProbability d ∧
      lightPairWeightBudget d ≤ 1 / 2 := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hd6 : (1 : ℝ) ≤ (d : ℝ) ^ 6 := one_le_pow₀ hd1
  have hd7 : (4 : ℝ) ≤ (d : ℝ) ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hdr 7
    norm_num at h
    linarith only [h]
  have hd13 : (2 : ℝ) ≤ (d : ℝ) ^ 13 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hdr 13
    norm_num at h
    linarith only [h]
  refine ⟨by unfold lightPairProbability; positivity,
    ?_, by unfold lightPairWeightBudget; positivity, ?_, ?_⟩
  · unfold lightPairProbability
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd6).trans_eq (by norm_num)
  · unfold lightPairWeightBudget lightPairProbability
    rw [mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hdp 13) (pow_pos hdp 6)).mpr
    have hm := mul_le_mul_of_nonneg_right hd7 (pow_nonneg hdp.le 6)
    have heq : (d : ℝ) ^ 13 = (d : ℝ) ^ 7 * (d : ℝ) ^ 6 := by rw [← pow_add]
    nlinarith only [hm, heq]
  · exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hd13

theorem light_pair_correction_bound (d : ℕ) (hd : 65536 ≤ d) (s : ℕ)
    (hs : (s : ℝ) ≤ 1024 * (d : ℝ) ^ 5) :
    Real.exp (2 * (lightPairWeightBudget d * s)) ≤ 2 := by
  have hdr : (4 : ℝ) ≤ d := by exact_mod_cast (show 4 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hd8 : (4096 : ℝ) ≤ (d : ℝ) ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hdr 8
    norm_num at h
    linarith only [h]
  have heq : (d : ℝ) ^ 13 = (d : ℝ) ^ 8 * (d : ℝ) ^ 5 := by rw [← pow_add]
  have hsmall : 2 * (lightPairWeightBudget d * s) ≤ 1 / 2 := by
    have hm := mul_le_mul_of_nonneg_right hd8 (pow_nonneg hdp.le 5)
    unfold lightPairWeightBudget
    rw [show 2 * (1 / (d : ℝ) ^ 13 * s) = (2 * s) / (d : ℝ) ^ 13 by ring]
    apply (div_le_iff₀ (pow_pos hdp 13)).mpr
    nlinarith only [hm, hs, heq]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact (Real.exp_le_exp.mpr (hsmall.trans hlog2)).trans_eq (Real.exp_log (by norm_num))

theorem light_pair_row_size_bound (d s : ℕ) (hd : 65536 ≤ d)
    (hs : s ≤ 1024 * d ^ 5) : s ≤ lightPairTailFactor d * (d / 4) := by
  have hquarter : d ≤ 8 * (d / 4) := by omega
  have hm := Nat.mul_le_mul_left (2048 * d ^ 4) hquarter
  unfold lightPairTailFactor
  rw [pow_succ] at hs
  nlinarith only [hs, hm]

theorem light_pair_tail_bound (d : ℕ) (hd : 65536 ≤ d) :
    ((lightPairTailFactor d : ℝ) * Real.exp 1 * lightPairProbability d) ^ (d / 4) ≤
      1 / (d : ℝ) ^ 8 := by
  have hdr : (49152 : ℝ) ≤ d := by exact_mod_cast (show 49152 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have ha : (lightPairTailFactor d : ℝ) = 16384 * (d : ℝ) ^ 4 := by simp [lightPairTailFactor]
  have hbase : (lightPairTailFactor d : ℝ) * Real.exp 1 * lightPairProbability d ≤ 1 / d := by
    unfold lightPairProbability
    rw [mul_one_div]
    apply (div_le_div_iff₀ (pow_pos hdp 6) hdp).mpr
    have he := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (show 0 ≤ 16384 * (d : ℝ) ^ 4 by positivity)
    have hl := mul_le_mul_of_nonneg_right hdr (pow_nonneg hdp.le 5)
    rw [ha]
    have hd6 : (d : ℝ) ^ 6 = (d : ℝ) * (d : ℝ) ^ 5 := by ring
    have hscaled := mul_le_mul_of_nonneg_right he hdp.le
    nlinarith only [hscaled, hl, hd6]
  have hbase0 : 0 ≤ (lightPairTailFactor d : ℝ) * Real.exp 1 * lightPairProbability d := by
    unfold lightPairProbability
    positivity
  have hinv : 1 / (d : ℝ) ≤ 1 := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hd1).trans_eq (by norm_num)
  calc
    _ ≤ (1 / (d : ℝ)) ^ (d / 4) := pow_le_pow_left₀ hbase0 hbase _
    _ ≤ (1 / (d : ℝ)) ^ 8 := pow_le_pow_of_le_one (by positivity) hinv (by omega)
    _ = _ := by rw [div_pow, one_pow]

end Erdos911
