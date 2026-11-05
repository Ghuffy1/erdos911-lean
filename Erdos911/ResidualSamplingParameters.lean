import Erdos911.ResidualParameterBounds
import Erdos911.CandidateSampling

namespace Erdos911

theorem baselineSampleRate_mul (A : ℕ) (x : ℝ) (hx : x ≠ 0) :
    baselineSampleRate A x * x = baselineSampleConstant A * Real.log x := by
  unfold baselineSampleRate
  exact div_mul_cancel₀ _ hx

theorem baselineSampleRate_pos (A d : ℕ) (hd : 0 < d) (hlog : 1 ≤ Real.log d) :
    0 < baselineSampleRate A d := by
  unfold baselineSampleRate
  exact div_pos (mul_pos (baselineSampleConstant_pos A) (by linarith))
    (by exact_mod_cast hd)

theorem baselineSampleRate_degree (A d : ℕ) (hd : 0 < d) (hlog : 1 ≤ Real.log d) :
    3 ≤ baselineSampleRate A d * d := by
  rw [baselineSampleRate_mul A d (by exact_mod_cast hd.ne')]
  have hconstant : 3 ≤ baselineSampleConstant A := by
    unfold baselineSampleConstant
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    nlinarith
  nlinarith [baselineSampleConstant_pos A]

theorem baselineSeedOrder_bounds (A d k : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hdk : d ≤ k) (hα : baselineSampleRate A d ≤ 1 / 5) :
    4 * baselineSampleRate A d * k ≤ (baselineSeedOrder A d k : ℝ) ∧
      (baselineSeedOrder A d k : ℝ) ≤ 5 * baselineSampleRate A d * k ∧
        baselineSeedOrder A d k ≤ k := by
  have hαpos := baselineSampleRate_pos A d hd hlog
  have hdkreal : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hlarge : 1 ≤ baselineSampleRate A d * k := by
    have h := mul_le_mul_of_nonneg_left hdkreal hαpos.le
    linarith [baselineSampleRate_degree A d hd hlog]
  have hlower := Nat.le_ceil (4 * baselineSampleRate A d * k)
  have hupper := (Nat.ceil_lt_add_one
    (show 0 ≤ 4 * baselineSampleRate A d * k by positivity)).le
  refine ⟨hlower, ?_, ?_⟩
  · change (Nat.ceil (4 * baselineSampleRate A d * k) : ℝ) ≤ _
    linarith
  · apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) k)
    linarith

theorem baseline_candidate_failure_budget (A d D : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hD : d ≤ D) (hDpow : D ≤ d ^ A) :
    (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128) ≤
      1 / (d : ℝ) := by
  apply candidate_failure_budget d D hd hD (baselineSampleRate A d) (1 / 16)
  have hDlog := log_polynomial_successor_le A d D (by omega) hDpow
  rw [baselineSampleRate_mul A d (by exact_mod_cast hd.ne')]
  unfold baselineSampleConstant
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  nlinarith

theorem baseline_seed_sampling_bound (A d D k : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hD : d ≤ D) (hDpow : D ≤ d ^ A) :
    3 * k * (baselineSampleRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128)) ≤
      (baselineSeedOrder A d k : ℝ) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hfailure := baseline_candidate_failure_budget A d D hd hlog hD hDpow
  have hα := baselineSampleRate_degree A d hd hlog
  have hsmall : 3 / (d : ℝ) ≤ baselineSampleRate A d := (div_le_iff₀ hdreal).mpr hα
  have hscaled := mul_le_mul_of_nonneg_left hfailure
    (show 0 ≤ 3 * (k : ℝ) by positivity)
  have hsmallscaled := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg (α := ℝ) k)
  have hceil := Nat.le_ceil (4 * baselineSampleRate A d * k)
  change _ ≤ (Nat.ceil (4 * baselineSampleRate A d * k) : ℝ)
  calc
    3 * k * (baselineSampleRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128)) =
        3 * k * baselineSampleRate A d + 3 * k * ((4 * (D * D : ℕ) + 1 : ℝ) *
          Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128)) := by ring
    _ ≤ 3 * k * baselineSampleRate A d + 3 * k * (1 / (d : ℝ)) :=
      add_le_add le_rfl hscaled
    _ = 3 * k * baselineSampleRate A d + k * (3 / (d : ℝ)) := by ring
    _ ≤ 3 * k * baselineSampleRate A d + k * baselineSampleRate A d :=
      add_le_add le_rfl hsmallscaled
    _ = 4 * baselineSampleRate A d * k := by ring
    _ ≤ _ := hceil

end Erdos911
