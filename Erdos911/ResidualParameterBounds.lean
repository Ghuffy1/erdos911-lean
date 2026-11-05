import Erdos911.SeedCountLogBounds
import Erdos911.PolynomialEntropyThreshold

open Filter Asymptotics

namespace Erdos911

noncomputable def baselineSampleConstant (A : ℕ) : ℝ := 1048576 * (A + 1)

noncomputable def baselineSampleRate (A : ℕ) (x : ℝ) : ℝ :=
  baselineSampleConstant A * Real.log x / x

noncomputable def baselineResidualRate (x : ℝ) : ℝ := 256 * Real.log (Real.log x) / x

noncomputable def baselineBlockSize (x : ℝ) : ℕ := Nat.ceil ((Real.log x) ^ 4)

noncomputable def baselineSeedOrder (A d k : ℕ) : ℕ :=
  Nat.ceil (4 * baselineSampleRate A d * k)

noncomputable def baselineResidualError (A : ℕ) (x : ℝ) : ℝ :=
  (((A : ℝ) + 3) * Real.log x + 4 +
    5 * baselineSampleConstant A * Real.log x * (4 * A * Real.log x + 1)) / x

theorem baselineSampleConstant_pos (A : ℕ) : 0 < baselineSampleConstant A := by
  unfold baselineSampleConstant
  positivity

theorem baselineSampleRate_tends_to_zero (A : ℕ) :
    Tendsto (baselineSampleRate A) atTop (nhds 0) :=
  biased_probability_tends_to_zero (baselineSampleConstant A)

theorem baselineResidualRate_tends_to_zero :
    Tendsto baselineResidualRate atTop (nhds 0) := by
  have hcomp : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x => Real.log x) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have h : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x => x) :=
    hcomp.trans Real.isLittleO_log_id_atTop
  change Tendsto (fun x : ℝ => 256 * Real.log (Real.log x) / x) atTop (nhds 0)
  simpa only [mul_zero, mul_div_assoc] using
    h.tendsto_div_nhds_zero.const_mul 256

theorem baselineResidualError_tends_to_zero (A : ℕ) :
    Tendsto (baselineResidualError A) atTop (nhds 0) := by
  have htwo : Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hone : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hzero : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h := ((htwo.const_mul (20 * A * baselineSampleConstant A)).add
    (hone.const_mul (A + 3 + 5 * baselineSampleConstant A))).add (hzero.const_mul 4)
  have heq : baselineResidualError A = fun x =>
      20 * A * baselineSampleConstant A * ((Real.log x) ^ 2 / x) +
      (A + 3 + 5 * baselineSampleConstant A) * (Real.log x / x) + 4 * (1 / x) := by
    funext x
    unfold baselineResidualError
    ring
  rw [heq]
  simpa only [mul_zero, add_zero] using h

theorem baselineBlockSize_ratio_tends_to_zero :
    Tendsto (fun x : ℝ => (baselineBlockSize x : ℝ) / x) atTop (nhds 0) := by
  have hfour : Tendsto (fun x : ℝ => (Real.log x) ^ 4 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero
  have hzero : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have hsum : Tendsto (fun x : ℝ => (Real.log x) ^ 4 / x + 1 / x) atTop (nhds 0) := by
    simpa only [add_zero] using hfour.add hzero
  apply squeeze_zero' ?_ ?_ hsum
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) hx.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (Real.log x) ^ 4 by positivity)).le
    calc
      (baselineBlockSize x : ℝ) / x ≤ ((Real.log x) ^ 4 + 1) / x :=
        div_le_div_of_nonneg_right hceil hx.le
      _ = (Real.log x) ^ 4 / x + 1 / x := by ring

theorem baselineBlockSize_log_bound (x : ℝ) (hlog : 1 ≤ Real.log x)
    (hx : 1 ≤ Real.log (Real.log x)) :
    Real.log ((baselineBlockSize x : ℝ) + 1) ≤ 6 * Real.log (Real.log x) := by
  have hlogpos : 0 < Real.log x := by linarith
  have hpow : (1 : ℝ) ≤ (Real.log x) ^ 4 := one_le_pow₀ hlog
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (Real.log x) ^ 4 by positivity)).le
  have hupper : (baselineBlockSize x : ℝ) + 1 ≤ 3 * (Real.log x) ^ 4 := by
    change (Nat.ceil ((Real.log x) ^ 4) : ℝ) + 1 ≤ _
    linarith
  have hthree := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  norm_num at hthree
  calc
    Real.log ((baselineBlockSize x : ℝ) + 1) ≤ Real.log (3 * (Real.log x) ^ 4) :=
      Real.log_le_log (by positivity) hupper
    _ = Real.log 3 + 4 * Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) (pow_pos hlogpos _).ne', Real.log_pow]
      norm_num
    _ ≤ 6 * Real.log (Real.log x) := by linarith

end Erdos911
