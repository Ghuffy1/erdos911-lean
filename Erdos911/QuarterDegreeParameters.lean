import Erdos911.PolynomialComponentPalette

namespace Erdos911

theorem quarter_degree_parameter_bounds (B d : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hd : 25 ≤ d) (hpower : 5 ^ (B + 1) ≤ d) :
    1 ≤ d / 4 ∧ d ≤ 5 * (d / 4) ∧ d ^ B ≤ (d / 4) ^ (B + 1) ∧
      Real.log d ≤ 2 * Real.log (d / 4 : ℕ) ∧
      (Nat.ceil (C * Real.log d) : ℝ) ≤ 2 * (C + 1) * Real.log (d / 4 : ℕ) := by
  let q := d / 4
  have hq5 : 5 ≤ q := by dsimp only [q]; omega
  have hdq : d ≤ 5 * q := by dsimp only [q]; omega
  have hpq : 5 ^ B ≤ q := by
    rw [pow_succ] at hpower
    omega
  have hp₁ := Nat.pow_le_pow_left hdq B
  rw [mul_pow] at hp₁
  have hp₂ := Nat.mul_le_mul_right (q ^ B) hpq
  have hmax : d ^ B ≤ q ^ (B + 1) := by
    rw [pow_succ]
    nlinarith only [hp₁, hp₂]
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqsq : (d : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hqr : (5 : ℝ) ≤ q := by exact_mod_cast hq5
    have hdr : (d : ℝ) ≤ 5 * q := by exact_mod_cast hdq
    nlinarith only [hqr, hdr]
  have hlog := Real.log_le_log hdp hqsq
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogd : 1 ≤ Real.log d := by
    have he : Real.exp 1 ≤ (d : ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ d by omega))
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ C * Real.log d by positivity)).le
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C + 1 by linarith)
  refine ⟨by omega, hdq, hmax, hlog, ?_⟩
  nlinarith only [hceil, hlogd, hm]

end Erdos911
