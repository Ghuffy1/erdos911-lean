import Erdos911.ResidualSamplingParameters
import Mathlib.Analysis.Real.Sqrt

open Filter

namespace Erdos911

noncomputable def tolerantSamplingError (x : ℝ) : ℝ := (Real.sqrt (Real.log x))⁻¹

noncomputable def tolerantSamplingRate (A : ℕ) (x : ℝ) : ℝ :=
  baselineSampleConstant A * (Real.log x) ^ 2 / x

noncomputable def tolerantSamplingSeed (A d k : ℕ) : ℕ :=
  Nat.ceil (4 * tolerantSamplingRate A d * k)

noncomputable def tolerantTupleOrder (x : ℝ) : ℕ := Nat.floor (Real.sqrt (Real.log x) / 20)

theorem tolerantSamplingError_pos (x : ℝ) (hlog : 0 < Real.log x) :
    0 < tolerantSamplingError x := inv_pos.mpr (Real.sqrt_pos.mpr hlog)

theorem tolerantSamplingRate_pos (A : ℕ) (x : ℝ) (hx : 0 < x) (hlog : 0 < Real.log x) :
    0 < tolerantSamplingRate A x := by
  unfold tolerantSamplingRate
  exact div_pos (mul_pos (baselineSampleConstant_pos A) (sq_pos_of_pos hlog)) hx

theorem tolerantSamplingRate_mul (A : ℕ) (x : ℝ) (hx : x ≠ 0) :
    tolerantSamplingRate A x * x = baselineSampleConstant A * (Real.log x) ^ 2 := by
  unfold tolerantSamplingRate
  exact div_mul_cancel₀ _ hx

theorem tolerantSamplingError_rate (A : ℕ) (x : ℝ) (hx : 0 < x) (hlog : 0 < Real.log x) :
    (tolerantSamplingError x) ^ 2 * (tolerantSamplingRate A x * x) =
      baselineSampleConstant A * Real.log x := by
  rw [tolerantSamplingRate_mul A x hx.ne']
  unfold tolerantSamplingError
  rw [inv_pow, Real.sq_sqrt hlog.le]
  field_simp

theorem tolerantSamplingRate_tends_to_zero (A : ℕ) :
    Tendsto (tolerantSamplingRate A) atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => baselineSampleConstant A * (Real.log x) ^ 2 / x) atTop (nhds 0)
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  simpa only [one_mul, add_zero, mul_zero, ← mul_div_assoc] using
    h.const_mul (baselineSampleConstant A)

theorem tolerantSamplingError_tends_to_zero :
    Tendsto tolerantSamplingError atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)

theorem tolerantTupleOrder_error (x : ℝ) (hlog : 0 < Real.log x) :
    (tolerantTupleOrder x : ℝ) * (5 * tolerantSamplingError x) ≤ 1 / 4 := by
  have hsqrt : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlog
  have hfloor : (tolerantTupleOrder x : ℝ) ≤ Real.sqrt (Real.log x) / 20 :=
    Nat.floor_le (by positivity)
  calc
    _ ≤ (Real.sqrt (Real.log x) / 20) * (5 * tolerantSamplingError x) :=
      mul_le_mul_of_nonneg_right hfloor (by unfold tolerantSamplingError; positivity)
    _ = 1 / 4 := by unfold tolerantSamplingError; field_simp; ring

theorem tolerantSamplingSeed_bounds (A d k : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hdk : d ≤ k) (hα : tolerantSamplingRate A d ≤ 1 / 5) :
    4 * tolerantSamplingRate A d * k ≤ (tolerantSamplingSeed A d k : ℝ) ∧
      (tolerantSamplingSeed A d k : ℝ) ≤ 5 * tolerantSamplingRate A d * k ∧
      tolerantSamplingSeed A d k ≤ k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hαpos := tolerantSamplingRate_pos A d hdR (by linarith)
  have hconstant : 3 ≤ baselineSampleConstant A := by
    unfold baselineSampleConstant
    have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    nlinarith
  have hmean : 3 ≤ tolerantSamplingRate A d * d := by
    rw [tolerantSamplingRate_mul A d hdR.ne']
    nlinarith [baselineSampleConstant_pos A]
  have hlarge : 1 ≤ tolerantSamplingRate A d * k := by
    have h := mul_le_mul_of_nonneg_left (show (d : ℝ) ≤ k by exact_mod_cast hdk) hαpos.le
    linarith
  have hlower := Nat.le_ceil (4 * tolerantSamplingRate A d * k)
  have hupper := (Nat.ceil_lt_add_one
    (show 0 ≤ 4 * tolerantSamplingRate A d * k by positivity)).le
  refine ⟨hlower, ?_, ?_⟩
  · change (Nat.ceil (4 * tolerantSamplingRate A d * k) : ℝ) ≤ _
    linarith
  · apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) k)
    linarith

theorem tolerant_sampling_seed_bound (A d D k : ℕ) (hd : 0 < d)
    (hlog : 1 ≤ Real.log d) (hD : d ≤ D) (hDpow : D ≤ d ^ A) :
    3 * k * (tolerantSamplingRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((tolerantSamplingError d) ^ 2 * (tolerantSamplingRate A d * d)) / 128)) ≤
      (tolerantSamplingSeed A d k : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfailure := candidate_failure_budget d D hd hD (tolerantSamplingRate A d) (tolerantSamplingError d)
    (by
      rw [tolerantSamplingError_rate A d hdR (by linarith)]
      have hbound := log_polynomial_successor_le A d D (by omega) hDpow
      unfold baselineSampleConstant
      nlinarith [Nat.cast_nonneg (α := ℝ) A])
  have hmean : 3 ≤ tolerantSamplingRate A d * d := by
    rw [tolerantSamplingRate_mul A d hdR.ne']
    have hconstant : 3 ≤ baselineSampleConstant A := by
      unfold baselineSampleConstant
      have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
      nlinarith
    nlinarith [baselineSampleConstant_pos A]
  have hsmall : 3 / (d : ℝ) ≤ tolerantSamplingRate A d := (div_le_iff₀ hdR).mpr (by nlinarith)
  have hscaled := mul_le_mul_of_nonneg_left hfailure (show 0 ≤ 3 * (k : ℝ) by positivity)
  have hsmallscaled := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg (α := ℝ) k)
  have hceil := Nat.le_ceil (4 * tolerantSamplingRate A d * k)
  change _ ≤ (Nat.ceil (4 * tolerantSamplingRate A d * k) : ℝ)
  calc
    _ ≤ 3 * k * tolerantSamplingRate A d + 3 * k * (1 / (d : ℝ)) := by nlinarith only [hscaled]
    _ = 3 * k * tolerantSamplingRate A d + k * (3 / (d : ℝ)) := by ring
    _ ≤ 4 * tolerantSamplingRate A d * k := by nlinarith only [hsmallscaled]
    _ ≤ _ := hceil

theorem tolerant_sampling_parameters_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D k : ℕ, d ≤ D → D ≤ d ^ A → d ≤ k →
      1 ≤ d ∧ 1 ≤ Real.log d ∧ 0 < tolerantSamplingError d ∧ tolerantSamplingError d < 1 / 5 ∧
      0 < tolerantSamplingRate A d ∧ tolerantSamplingRate A d ≤ 1 / 5 ∧
      2 ≤ tolerantTupleOrder d ∧
      (tolerantTupleOrder d : ℝ) * (5 * tolerantSamplingError d) ≤ 1 / 4 ∧
      tolerantSamplingSeed A d k ≤ k ∧
      (tolerantSamplingSeed A d k : ℝ) ≤ (5 * baselineSampleConstant A) * k * (Real.log d) ^ 2 / d ∧
      3 * k * (tolerantSamplingRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((tolerantSamplingError d) ^ 2 * (tolerantSamplingRate A d * d)) / 128)) ≤
          (tolerantSamplingSeed A d k : ℝ) := by
  have herror := tolerantSamplingError_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 5 by norm_num))
  have hrate := (tolerantSamplingRate_tends_to_zero A).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 5 by norm_num))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1600 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (herror.and (hrate.and hlog))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd D k hD hDpow hdk
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hd)
  obtain ⟨he, hα, hL⟩ := hx₀ d hx
  have hlog1 : 1 ≤ Real.log d := by linarith
  have htuple : 2 ≤ tolerantTupleOrder d := by
    apply Nat.le_floor
    have hsqrt : (40 : ℝ) ≤ Real.sqrt (Real.log d) := by
      apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
      norm_num
      exact hL
    linarith
  obtain ⟨_, hseed, hseedk⟩ := tolerantSamplingSeed_bounds A d k (by omega) hlog1 hdk hα.le
  refine ⟨hd1, hlog1, tolerantSamplingError_pos d (by linarith), he,
    tolerantSamplingRate_pos A d hdR (by linarith), hα.le, htuple,
    tolerantTupleOrder_error d (by linarith), hseedk, ?_,
    tolerant_sampling_seed_bound A d D k (by omega) hlog1 hD hDpow⟩
  apply hseed.trans_eq
  unfold tolerantSamplingRate
  ring

end Erdos911
