import Erdos911.AdaptiveSampling
import Erdos911.TolerantSamplingParameters

namespace Erdos911

/-- The same sampling rate pays for the additional absolute high-neighbor
count and the weaker exponent in the adaptive fraction estimate. -/
theorem incidence_adaptive_seed_bound (A d D k : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hD : d ≤ D) (hDpow : D ≤ d ^ A)
    (herror : tolerantSamplingError d ≤ 1) :
    3 * k * (tolerantSamplingRate A d + Real.exp (-(tolerantSamplingRate A d * d)) +
      2 * Real.exp (-(tolerantSamplingRate A d * d) / 2048) +
      (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((tolerantSamplingError d) ^ 2 * (tolerantSamplingRate A d * d)) / 512)) ≤
      (tolerantSamplingSeed A d k : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp := tolerantSamplingRate_pos A d hdR (by linarith)
  have he := tolerantSamplingError_pos d (by linarith)
  have hsample : 4 * Real.log ((D : ℝ) + 1) ≤
      (tolerantSamplingError d) ^ 2 * (tolerantSamplingRate A d * d) / 512 := by
    rw [tolerantSamplingError_rate A d hdR (by linarith)]
    have hbound := log_polynomial_successor_le A d D (by omega) hDpow
    unfold baselineSampleConstant
    nlinarith [Nat.cast_nonneg (α := ℝ) A]
  have hfailure := adaptive_failure_budget d D hd hD (tolerantSamplingRate A d)
    (tolerantSamplingError d) hp.le he.le herror hsample
  have hmean : 12 ≤ tolerantSamplingRate A d * d := by
    rw [tolerantSamplingRate_mul A d hdR.ne']
    have hconstant : 12 ≤ baselineSampleConstant A := by
      unfold baselineSampleConstant
      have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      nlinarith
    have hL : (1 : ℝ) ≤ (Real.log d) ^ 2 := one_le_pow₀ hlog
    nlinarith [baselineSampleConstant_pos A]
  have hsmall : 12 / (d : ℝ) ≤ tolerantSamplingRate A d := (div_le_iff₀ hdR).mpr hmean
  have hscaled := mul_le_mul_of_nonneg_left hfailure (show 0 ≤ 3 * (k : ℝ) by positivity)
  have hsmallscaled := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg (α := ℝ) k)
  have hceil := Nat.le_ceil (4 * tolerantSamplingRate A d * k)
  change _ ≤ (Nat.ceil (4 * tolerantSamplingRate A d * k) : ℝ)
  calc
    _ ≤ 3 * k * tolerantSamplingRate A d + 3 * k * (4 / (d : ℝ)) := by
      nlinarith only [hscaled]
    _ = 3 * k * tolerantSamplingRate A d + k * (12 / (d : ℝ)) := by ring
    _ ≤ 4 * tolerantSamplingRate A d * k := by nlinarith only [hsmallscaled]
    _ ≤ _ := hceil

theorem incidence_sampling_parameters_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D k : ℕ, d ≤ D → D ≤ d ^ A → d ≤ k →
      1 ≤ d ∧ 1 ≤ Real.log d ∧ 0 < tolerantSamplingError d ∧ tolerantSamplingError d < 1 / 5 ∧
      0 < tolerantSamplingRate A d ∧ tolerantSamplingRate A d ≤ 1 / 5 ∧
      2 ≤ tolerantTupleOrder d ∧
      (tolerantTupleOrder d : ℝ) * (5 * tolerantSamplingError d) ≤ 1 / 4 ∧
      tolerantSamplingSeed A d k ≤ k ∧
      (tolerantSamplingSeed A d k : ℝ) ≤ (5 * baselineSampleConstant A) * k * (Real.log d) ^ 2 / d ∧
      3 * k * (tolerantSamplingRate A d + Real.exp (-(tolerantSamplingRate A d * d)) +
        2 * Real.exp (-(tolerantSamplingRate A d * d) / 2048) +
        (4 * (D * D : ℕ) + 1 : ℝ) *
          Real.exp (-((tolerantSamplingError d) ^ 2 * (tolerantSamplingRate A d * d)) / 512)) ≤
            (tolerantSamplingSeed A d k : ℝ) := by
  obtain ⟨d₀, hparams⟩ := tolerant_sampling_parameters_uniform A
  refine ⟨d₀, ?_⟩
  intro d hd D k hD hDpow hdk
  obtain ⟨hd1, hlog, he₀, he₁, hp₀, hp₁, hr, hbudget, hsk, hsbound, _⟩ :=
    hparams d hd D k hD hDpow hdk
  exact ⟨hd1, hlog, he₀, he₁, hp₀, hp₁, hr, hbudget, hsk, hsbound,
    incidence_adaptive_seed_bound A d D k (by omega) hlog hD hDpow (by linarith)⟩

end Erdos911
