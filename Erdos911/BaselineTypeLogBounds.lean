import Erdos911.BaselineTypeRatios

open Filter

namespace Erdos911

theorem baseline_available_log_bounds (B d k a : ℕ) (hd : 1 ≤ d) (ha : 0 < a)
    (hlog : 1 ≤ Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hΛ₀ : 1 ≤ baselineHostMultiplier d) (hΛ₁ : baselineHostMultiplier d ≤ d)
    (haverage : d * k ≤ 2 * a) (hdensity : (a : ℝ) ≤ baselineTargetDensity B d * k) :
    Real.log (((baselineDensityCutoff B d * k : ℕ) : ℝ) / a) ≤
      Real.log d + Real.log (Real.log d) + Real.log (baselineTypeLogConstant B) ∧
    Real.log d - 13 * Real.log (Real.log d) - Real.log 16384 ≤
      Real.log (((baselineDensityCutoff B d * k : ℕ) : ℝ) /
        ((a : ℝ) * (baselineBlockSize d * baselineBlockSize d : ℕ))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hLpos : 0 < Real.log d := by linarith
  have hUpos : 0 < Real.log (Real.log d) := by linarith
  have hΛpos : 0 < baselineHostMultiplier d := by linarith
  have hCpos : 0 < baselineTypeLogConstant B := by unfold baselineTypeLogConstant; positivity
  have hqpos : (0 : ℝ) < baselineBlockSize d :=
    (pow_pos hLpos 4).trans_le (Nat.le_ceil ((Real.log d) ^ 4))
  have hqnat : 0 < baselineBlockSize d := by exact_mod_cast hqpos
  have hRnat : 0 < baselineBlockSize d * baselineBlockSize d := Nat.mul_pos hqnat hqnat
  have hRpos : (0 : ℝ) < (baselineBlockSize d * baselineBlockSize d : ℕ) := by exact_mod_cast hRnat
  have hsmall := baseline_available_ratio_lower B d k a 1 ha (by omega) hΛpos.le hdensity
  have hMpos : 0 < ((baselineDensityCutoff B d * k : ℕ) : ℝ) / a := by
    have hsmall' : 32 * baselineHostMultiplier d ≤ ((baselineDensityCutoff B d * k : ℕ) : ℝ) / a := by
      simpa only [Nat.cast_one, div_one, mul_one] using hsmall
    exact (mul_pos (by norm_num) hΛpos).trans_le hsmall'
  constructor
  · have hupper := Real.log_le_log hMpos
      (baseline_available_ratio_upper B d k a hd ha hlog hΛ₀ hΛ₁ haverage)
    have heq : Real.log (baselineTypeLogConstant B * d * Real.log d) =
        Real.log d + Real.log (Real.log d) + Real.log (baselineTypeLogConstant B) := by
      rw [Real.log_mul (mul_pos hCpos hdpos).ne' hLpos.ne', Real.log_mul hCpos.ne' hdpos.ne']
      ring
    exact hupper.trans_eq heq
  · have hpair := Real.log_le_log (div_pos (mul_pos (by norm_num) hΛpos) hRpos)
      (baseline_available_ratio_lower B d k a (baselineBlockSize d * baselineBlockSize d)
        ha hRnat hΛpos.le hdensity)
    have hlogΛ : Real.log (baselineHostMultiplier d) =
        Real.log d - Real.log 16384 - Real.log (Real.log (Real.log d)) := by
      unfold baselineHostMultiplier
      rw [Real.log_div hdpos.ne' (mul_pos (by norm_num) hUpos).ne',
        Real.log_mul (by norm_num) hUpos.ne']
      ring
    have hlogq : Real.log (baselineBlockSize d) ≤ 6 * Real.log (Real.log d) :=
      (Real.log_le_log hqpos (by linarith : (baselineBlockSize d : ℝ) ≤
        (baselineBlockSize d : ℝ) + 1)).trans (baselineBlockSize_log_bound d hlog hloglog)
    have hlogR : Real.log ((baselineBlockSize d * baselineBlockSize d : ℕ) : ℝ) ≤
        12 * Real.log (Real.log d) := by
      rw [Nat.cast_mul, Real.log_mul hqpos.ne' hqpos.ne']
      linarith
    rw [Real.log_div (mul_pos (by norm_num) hΛpos).ne' hRpos.ne',
      Real.log_mul (by norm_num) hΛpos.ne', hlogΛ] at hpair
    have hlogU := Real.log_le_sub_one_of_pos hUpos
    have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    linarith

noncomputable def baselineTypeLogError (B : ℕ) (x : ℝ) : ℝ :=
  14 * (Real.log (Real.log x) + Real.log (baselineTypeLogConstant B) + Real.log 16384) / Real.log x

theorem baselineTypeLogError_tends_to_zero (B : ℕ) :
    Tendsto (baselineTypeLogError B) atTop (nhds 0) := by
  have h := (component_entropy_error_tends_to_zero
    (Real.log (baselineTypeLogConstant B) + Real.log 16384)).const_mul 14
  change Tendsto (fun x : ℝ => 14 *
    (Real.log (Real.log x) + Real.log (baselineTypeLogConstant B) + Real.log 16384) / Real.log x)
    atTop (nhds 0)
  simpa only [mul_zero, mul_div_assoc, add_assoc] using h

theorem eventually_baseline_type_log_bounds (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k a : ℕ, 0 < a → d * k ≤ 2 * a →
      (a : ℝ) ≤ baselineTargetDensity B d * k →
      Real.log (((baselineDensityCutoff B d * k : ℕ) : ℝ) / a) ≤
        (1 + 1 / 8192 : ℝ) * Real.log d ∧
      (1 - 1 / 8192 : ℝ) * Real.log d ≤
        Real.log (((baselineDensityCutoff B d * k : ℕ) : ℝ) /
          ((a : ℝ) * (baselineBlockSize d * baselineBlockSize d : ℕ))) := by
  obtain ⟨d₁, hd₁⟩ := eventually_baseline_host_parameters
  have herr := (baselineTypeLogError_tends_to_zero B).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 8192 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp herr
  refine ⟨max d₁ (Nat.ceil x₀), ?_⟩
  intro d hd k a ha haverage hdensity
  obtain ⟨hdlarge, hlog, hloglog, hΛ₀, hΛ₁⟩ := hd₁ d ((le_max_left _ _).trans hd)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans
    (by exact_mod_cast (le_max_right d₁ (Nat.ceil x₀)).trans hd)
  have he := hx₀ d hx
  unfold baselineTypeLogError at he
  have herror := (div_lt_iff₀ (show 0 < Real.log d by linarith)).mp he
  have hC : 0 ≤ Real.log (baselineTypeLogConstant B) := by
    apply Real.log_nonneg
    unfold baselineTypeLogConstant
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith
  have hconstant : 0 ≤ Real.log (16384 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨hupper, hlower⟩ := baseline_available_log_bounds B d k a (by omega) ha
    (by linarith) hloglog hΛ₀ hΛ₁ haverage hdensity
  constructor <;> linarith

end Erdos911
