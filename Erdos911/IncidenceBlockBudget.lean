import Erdos911.NearRegularBlockBudget

open Filter

namespace Erdos911

noncomputable def incidenceBlockRate (A : ℕ) (d : ℝ) : ℝ :=
  ((A : ℝ) + 1) * nearRegularBlockRate d

theorem incidence_block_rate_scale (A d D : ℕ) (hd : 1 ≤ d) (hD : 0 < D)
    (hDpow : D ≤ d ^ A) (hlog : 0 < Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hlarge : 1024 ≤ nearRegularLossFraction 1024 d * d) :
    32 * Real.log D ≤ incidenceBlockRate A d * nearRegularEffectiveDegree d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    apply (Real.log_le_log hDpos (show (D : ℝ) ≤ (d : ℝ) ^ A by exact_mod_cast hDpow)).trans_eq
    rw [Real.log_pow]
  have hp : 0 ≤ incidenceBlockRate A d := by unfold incidenceBlockRate nearRegularBlockRate; positivity
  have hlower := mul_le_mul_of_nonneg_left
    (near_regular_effective_degree_lower d hdpos hlog hloglog hlarge) hp
  have heq : incidenceBlockRate A d * (8 * d / Real.log d) =
      128 * ((A : ℝ) + 1) * Real.log d := by
    unfold incidenceBlockRate nearRegularBlockRate
    field_simp
    ring
  rw [heq] at hlower
  have hAlog : 0 ≤ (A : ℝ) * Real.log d := mul_nonneg (Nat.cast_nonneg _) hlog.le
  nlinarith only [hlower, hlogD, hAlog, hlog]

theorem incidence_block_parameters_uniform (A : ℕ) (M C : ℝ) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℕ, d ≤ D → D ≤ d ^ A →
      0 ≤ incidenceBlockRate A d ∧ incidenceBlockRate A d ≤ 1 ∧
      32 * Real.log D ≤ incidenceBlockRate A d * nearRegularEffectiveDegree d ∧
      ∀ m E : ℝ, 0 ≤ m → 0 ≤ E → m ≤ M * d * E →
        (2 * incidenceBlockRate A d) *
          (2 * (C * Real.log d) * m / ((1 / 4 : ℝ) * baselineBlockSize d) +
            2 * (C * Real.log d) * m / (nearRegularRectangleDensity d * nearRegularBlockSize d)) ≤
              (1 / 16 : ℝ) * E := by
  obtain ⟨dL, hdL⟩ := near_regular_loss_parameters_uniform
  have hpLimit : Tendsto (incidenceBlockRate A) atTop (nhds 0) := by
    change Tendsto (fun x => ((A : ℝ) + 1) * nearRegularBlockRate x) atTop (nhds 0)
    simpa only [incidenceBlockRate, mul_zero] using
      nearRegularBlockRate_tends_to_zero.const_mul ((A : ℝ) + 1)
  have hcostLimit : Tendsto (fun x => ((A : ℝ) + 1) * nearRegularBlockCost M C x) atTop (nhds 0) := by
    simpa only [mul_zero] using (nearRegularBlockCost_tends_to_zero M C).const_mul ((A : ℝ) + 1)
  have hp := hpLimit.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hcost := hcostLimit.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  have hlogs := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hp.and (hcost.and hlogs))
  refine ⟨max 2 (max dL (Nat.ceil x₀)), ?_⟩
  intro d hd D hdD hDpow
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd2)
  obtain ⟨_, _, _, hlarge⟩ := hdL d (by omega)
  obtain ⟨hp, hcost, hloglog⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ d by omega)))
  refine ⟨by unfold incidenceBlockRate nearRegularBlockRate; positivity, hp.le,
    incidence_block_rate_scale A d D (by omega) (by omega) hDpow hlog hloglog hlarge, ?_⟩
  intro m E hm hE hhost
  have h := mul_le_mul_of_nonneg_left (near_regular_two_scale_budget M C d m E hC hdpos hlog hm hhost)
    (show 0 ≤ (A : ℝ) + 1 by positivity)
  calc
    _ = ((A : ℝ) + 1) * ((2 * nearRegularBlockRate d) *
        (2 * (C * Real.log d) * m / ((1 / 4 : ℝ) * baselineBlockSize d) +
          2 * (C * Real.log d) * m / (nearRegularRectangleDensity d * nearRegularBlockSize d))) := by
      unfold incidenceBlockRate
      ring
    _ ≤ ((A : ℝ) + 1) * (nearRegularBlockCost M C d * E) := h
    _ ≤ (1 / 16 : ℝ) * E := by nlinarith only [mul_le_mul_of_nonneg_right hcost.le hE]

end Erdos911
