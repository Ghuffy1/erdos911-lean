import Erdos911.LightHostParameters

namespace Erdos911

theorem light_pair_entropy_gap (d D : ℕ) (hd : 65536 ≤ d) (hD : 2 ≤ D)
    (hupper : (D : ℝ) ≤ 4096 * (d : ℝ) ^ 20) :
    1024 * (Real.log D + Real.log 2) < (d : ℝ) ^ 7 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDp : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hd8 : (8 : ℝ) ≤ d := by exact_mod_cast (show 8 ≤ d by omega)
  have hlogD := Real.log_le_log hDp hupper
  rw [Real.log_mul (by norm_num) (pow_pos hdp 20).ne', Real.log_pow,
    show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.log_pow] at hlogD
  norm_num only [Nat.cast_ofNat] at hlogD
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hd2
  have hlogd : Real.log d ≤ (d : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hdp
    linarith only [h]
  have hlog : Real.log D + Real.log 2 ≤ 33 * (d : ℝ) := by
    linarith only [hlogD, hlog2, hlogd]
  have hpower : (33792 : ℝ) < (d : ℝ) ^ 6 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hd8 6
    norm_num at hp
    linarith only [hp]
  have hm := mul_lt_mul_of_pos_right hpower hdp
  have hseven : (d : ℝ) ^ 6 * d = (d : ℝ) ^ 7 := by ring
  rw [hseven] at hm
  linarith only [hlog, hm]

end Erdos911
