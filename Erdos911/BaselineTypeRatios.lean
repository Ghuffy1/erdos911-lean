import Erdos911.BaselineHostBounds
import Erdos911.RepeatedTypeParameters

open Filter

namespace Erdos911

noncomputable def baselineTypeLogConstant (B : ℕ) : ℝ := 262146 * ((B : ℝ) + 1)

theorem baselineDensityCutoff_upper (B d : ℕ) (hd : 1 ≤ d) (hlog : 1 ≤ Real.log d)
    (hΛ₀ : 1 ≤ baselineHostMultiplier d) (hΛ₁ : baselineHostMultiplier d ≤ d) :
    (baselineDensityCutoff B d : ℝ) ≤ 131073 * ((B : ℝ) + 1) * (d : ℝ) ^ 2 * Real.log d := by
  have hΛ : 0 ≤ baselineHostMultiplier d := by linarith
  have hσ : 0 ≤ baselineTargetDensity B d := by unfold baselineTargetDensity; positivity
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ 32 * baselineHostMultiplier d * baselineTargetDensity B d by positivity)).le
  have hpow := pow_le_pow_left₀ hΛ hΛ₁ 2
  have hscaled := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 131072 * ((B : ℝ) + 1) * Real.log d by positivity)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hdR
  have hB : 0 ≤ (B : ℝ) * (d : ℝ) ^ 2 := by positivity
  have hunitScale := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ ((B : ℝ) + 1) * (d : ℝ) ^ 2 by positivity)
  change (baselineDensityCutoff B d : ℝ) ≤ _ at hceil
  unfold baselineTargetDensity at hceil
  nlinarith only [hceil, hscaled, hd2, hB, hunitScale]

theorem baseline_available_ratio_upper (B d k a : ℕ) (hd : 1 ≤ d) (ha : 0 < a)
    (hlog : 1 ≤ Real.log d) (hΛ₀ : 1 ≤ baselineHostMultiplier d)
    (hΛ₁ : baselineHostMultiplier d ≤ d) (haverage : d * k ≤ 2 * a) :
    ((baselineDensityCutoff B d * k : ℕ) : ℝ) / a ≤
      baselineTypeLogConstant B * d * Real.log d := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hupper := baselineDensityCutoff_upper B d hd hlog hΛ₀ hΛ₁
  have hscaled := mul_le_mul_of_nonneg_right hupper (Nat.cast_nonneg (α := ℝ) k)
  have havg : (d : ℝ) * k ≤ 2 * a := by exact_mod_cast haverage
  have havgScaled := mul_le_mul_of_nonneg_left havg
    (show 0 ≤ 131073 * ((B : ℝ) + 1) * d * Real.log d by positivity)
  apply (div_le_iff₀ haR).mpr
  rw [Nat.cast_mul]
  unfold baselineTypeLogConstant
  nlinarith only [hscaled, havgScaled]

theorem baseline_available_ratio_lower (B d k a R : ℕ) (ha : 0 < a) (hR : 0 < R)
    (hΛ : 0 ≤ baselineHostMultiplier d)
    (hdensity : (a : ℝ) ≤ baselineTargetDensity B d * k) :
    32 * baselineHostMultiplier d / (R : ℝ) ≤
      ((baselineDensityCutoff B d * k : ℕ) : ℝ) / ((a : ℝ) * R) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hceil : 32 * baselineHostMultiplier d * baselineTargetDensity B d ≤
      (baselineDensityCutoff B d : ℝ) := Nat.le_ceil _
  have hdense := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 32 * baselineHostMultiplier d by positivity)
  have hceilScaled := mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg (α := ℝ) k)
  have hratio : 32 * baselineHostMultiplier d ≤ ((baselineDensityCutoff B d * k : ℕ) : ℝ) / a := by
    apply (le_div_iff₀ haR).mpr
    rw [Nat.cast_mul]
    nlinarith only [hdense, hceilScaled]
  simpa only [div_div] using div_le_div_of_nonneg_right hratio hRreal.le

end Erdos911
